# Configuring GCloud for Deploying Cloud Run service

> ![WARNING]
>
> Working with `gcloud` CLI requires specific version of python which
> can be set through `CLOUDSDK_PYTHON` pointing to the right version.


> ![WARNING]
>
> These instructions are somewhat incomplete and not fully tested,
> take with a grain of salt.

## Creating service account

To deploy built docker image from Github action:

```
export GCLOUD_SERVICE_ACCOUNT=peras-service-account@${GCLOUD_PROJECT_ID}.iam.gserviceaccount.com
export GCLOUD_COMPUTE_SERVICE_ACCOUNT=${GCLOUD_PROJECT_NUMBER}-compute@developer.gserviceaccount.com
gcloud iam service-accounts create "peras-service-account" --project "${GCLOUD_PROJECT_ID}"
```

Create a key

```
gcloud iam service-accounts keys create "peras-service-account.json" \
  --iam-account ${GCLOUD_SERVICE_ACCOUNT}
```

Give the service account the right set of permissions to:

* Manage the artifact registry
* Manage the Cloud Run service
* Create OAuth token to be used as part of the workflow

```
gcloud projects add-iam-policy-binding ${GCLOUD_PROJECT_ID} --member=serviceAccount:${GCLOUD_SERVICE_ACCOUNT} --role=roles/artifactregistry.admin
gcloud projects add-iam-policy-binding ${GCLOUD_PROJECT_ID} --member=serviceAccount:${GCLOUD_SERVICE_ACCOUNT} --role=roles/run.admin
gcloud projects add-iam-policy-binding ${GCLOUD_PROJECT_ID} --member=serviceAccount:${GCLOUD_SERVICE_ACCOUNT} --role=roles/iam.serviceAccountTokenCreator
```

Upload key as secret in the repository under name `GOOGLE_APPLICATION_CREDENTIALS`

[Permissions](https://cloud.google.com/run/docs/reference/iam/roles#additional-configuration) to set for deploying Cloud run:

```
gcloud run services add-iam-policy-binding peras-server --project="${GCLOUD_PROJECT_ID}" --region=us-east1 --role="roles/run.admin" --member=serviceAccount:${GCLOUD_SERVICE_ACCOUNT}
gcloud iam service-accounts  add-iam-policy-binding ${GCLOUD_COMPUTE_SERVICE_ACCOUNT}  --project="${GCLOUD_PROJECT_ID}"  --member=serviceAccount:${GCLOUD_SERVICE_ACCOUNT} --role="roles/iam.serviceAccountUser"
```

## Setting up artifacts repository

Cloud Run actions can only deploy from a GCloud docker registry, which are migrated to _Artifacts registry_.
To Create docker artifacts registry (need to enable Artifact registry API and authorise service account):

```
gcloud projects add-iam-policy-binding ${GCLOUD_PROJECT_ID} --member=serviceAccount:${GCLOUD_SERVICE_ACCOUNT} --role=roles/artifactregistry.admin
gcloud artifacts repositories create peras-docker --repository-format=docker \
    --location=us-east1 --description="Peras Docker repository" \
    --project=${GCLOUD_PROJECT_ID}
```

## Configuring Github action

As the GH action pushes the image to the GH docker repository, we would need to pull the image and then push it to our newly created repo

First we need to authenticate docker push, which can be done in various ways (checkout https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry#pushing-container-images for Github case). Locally, one can do:

```
gcloud auth print-access-token > pat
cat pat | docker login -u oauth2accesstoken --password-stdin https://us-east1-docker.pkg.dev
```

Then authenticate with gcloud:

```
gcloud auth application-default login
```

## Terraforming

Initialise terraform environment:

```
GOOGLE_APPLICATION_CREDENTIALS=./google-application-credentials.json TERRAFORM_BUCKET=peras_infra TERRAFORM_PREFIX=terraform/peras/state terraform init  \
   -backend-config="bucket=${TERRAFORM_BUCKET}" \
   -backend-config="prefix=${TERRAFORM_PREFIX}"
```

> ![NOTE]
> * The backend configuration cannot be set using "standard" terraform variables, so it must backend configuration variables
> * The bucket must exist before it can be used by terraform

Plan:

```
terraform plan -out plan
```

Execute:

```
terraform apply plan
```

Can take a while...

## References

* [build-push-action](https://github.com/docker/build-push-action)
* [deploy-cloudrun](https://github.com/google-github-actions/deploy-cloudrun) action
* [Google artifacts registry](https://cloud.google.com/artifact-registry/docs/docker/store-docker-container-images#gcloud)
* Authenticating to GCloud [github action](https://github.com/google-github-actions/auth)
* Terraform [cloud run](https://registry.terraform.io/providers/hashicorp/google/latest/docs/resources/cloud_run_v2_service) configuration
* Authenticating Docker to [Artifact registry](https://cloud.google.com/artifact-registry/docs/docker/authentication)
* Deploying a [Cloud run](https://cloud.google.com/run/docs/deploying#other-registries) service
