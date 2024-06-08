resource "google_cloud_run_v2_service" "peras_server" {
  name     = "peras-server"
  location = "us-east1"
  client   = "terraform"

  template {
    containers {
      image = "us-east1-docker.pkg.dev/iog-hydra/peras-docker/peras-design:latest"
      ports {
        container_port = 8091
      }
    }
  }
}

resource "google_cloud_run_v2_service_iam_member" "noauth" {
  location = google_cloud_run_v2_service.peras_server.location
  name     = google_cloud_run_v2_service.peras_server.name
  role     = "roles/run.invoker"
  member   = "allUsers"
}
