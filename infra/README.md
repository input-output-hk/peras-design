Working with [gcloud]() CLI requires specific version of python which can be set through `CLOUDSDK_PYTHON` pointing to the right version

Cloud Run actions can only deploy from a GCloud docker registry, which are migrated to _Artifacts registry_.

Create docker artifacts registry (need to enable Artifact registry API and authorise service account):

```
gcloud projects add-iam-policy-binding ${GCLOUD_PROJECT_ID} --member=serviceAccount:${GCLOUD_SERVICE_ACCOUNT} --role=roles/artifactregistry.admin
gcloud artifacts repositories create peras-docker --repository-format=docker \
    --location=us-east1 --description="Peras Docker repository" \
    --project=${GCLOUD_PROJECT_ID}
```

As the GH action pushes the image to the GH docker repository, we would need to pull the image and then push it to our newly created repo

First we need to authenticate docker push, which can be done in various ways (checkout https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry#pushing-container-images for Github case). Locally, one can do:

```
gcloud auth print-access-token > pat
cat pat | docker login -u oauth2accesstoken --password-stdin https://us-east1-docker.pkg.dev
```

Then

Authenticate with gcloud:

```
gcloud auth application-default login
```

Set policy for service account to administer cloud run resources

```
gcloud projects add-iam-policy-binding ${GCLOUD_PROJECT_ID} \
    --member=serviceAccount:${GCLOUD_SERVICE_ACCOUNT} \
    --role=roles/run.admin
```

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
